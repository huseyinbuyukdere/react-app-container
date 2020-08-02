import React, { useState } from 'react'
import styles from './menuExpandableItem.module.css'
import cn from 'classnames'
import { MenuItem as MenuItemContract } from '../../models'
import MenuItem from '../MenuItem'
import IconComponent from '../../icons'

interface MenuExpandableItemProps {
    label: string
    onClick: (routeKey?: string) => void
    iconComp?: any
    iconName?: string
    selectedRouteKey: string
    subMenuItemList: MenuItemContract[]
}

const MenuExpandableItem = (props: MenuExpandableItemProps) => {

    const isAnySelectedSubRoute = props.subMenuItemList.some((item) => item.routeKey === props.selectedRouteKey)
    const[isExpanded, setIsExpanded] = useState(isAnySelectedSubRoute);
    var maxListHeight=isExpanded ?`calc(2.2rem*${props.subMenuItemList.length})`: '0px';
    return (
        <div>
            <MenuItem
                label={props.label}
                iconComp={props.iconComp}
                iconName={props.iconName}
                rightIconName={isExpanded ? 'expand_less' : 'expand_more'}
                rightIconCompStyle = {{height:'18px',width:'18px'}}
                onClick={() => {
                    setIsExpanded(!isExpanded);
                }}
                isSelected={false}
            />
            <div className={cn(styles.listContainer)} style={{maxHeight:maxListHeight}}>
                {props.subMenuItemList.map((item) => {
                    var isSelected = props.selectedRouteKey === item.routeKey
                    var checkBoxIcon = (
                        <div
                            className={cn(
                                styles.subItemIconContainer,
                                isSelected && styles.selected
                            )}
                        >
                            <IconComponent
                                name="radio_button_checked"
                                height={8}
                                width={8}
                            />
                        </div>
                    )
                    return (
                        <div className={styles.menuItemContainer}>
                            <MenuItem
                                style={{ paddingLeft: '40px' }}
                                label={item.label}
                                iconComp={checkBoxIcon}
                                onClick={() => {
                                    props.onClick(item.routeKey)
                                }}
                                isSelected={isSelected}
                            />
                        </div>
                    )
                })}
            </div>
        </div>
    )
}

export default MenuExpandableItem

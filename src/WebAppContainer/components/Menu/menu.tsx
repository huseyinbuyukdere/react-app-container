import React from 'react'
import MenuItem from '../MenuItem'
import styles from './menu.module.css'
import { MenuItem as MenuItemContract } from '../../models'
import MenuExpandableItem from '../MenuExpandableItem'

interface MenuProps {
    itemList: MenuItemContract[]
    selectedRouteKey: string
    isFlat?: boolean
}

export default function Menu(props: MenuProps) {
    var itemList = props.itemList ? props.itemList : []
    itemList = itemList.filter((item) => (item.label && item.label!=='') || item.customComp);

    return (
        <div className={styles.menuContainer}>
            {itemList.map((item) => {
                return (
                    <React.Fragment>
                        {item.subMenuItemList ? (
                            <div>
                                <MenuExpandableItem
                                    iconComp={item.iconComp}
                                    iconName={item.iconName}
                                    label={item.label ? item.label : ''}
                                    subMenuItemList={item.subMenuItemList}
                                    selectedRouteKey={props.selectedRouteKey}
                                    onClick={(routeKey?: string) => {
                                        if (item.onClick) item.onClick(routeKey)
                                    }}
                                />
                            </div>
                        ) : (
                            <div className={styles.menuItemContainer}>
                                <MenuItem
                                    iconComp={item.iconComp}
                                    iconName={item.iconName}
                                    label={item.label ? item.label : ''}
                                    isFlat={props.isFlat}
                                    isSelected={
                                        props.selectedRouteKey ? item.routeKey === props.selectedRouteKey : false
                                    }
                                    onClick={(routeKey?: string) => {
                                        if (item.onClick) item.onClick(routeKey)
                                    }}
                                />
                            </div>
                        )}
                    </React.Fragment>
                )
            })}
        </div>
    )
}

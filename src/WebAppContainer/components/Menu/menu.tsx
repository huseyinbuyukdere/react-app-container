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

    return (
        <div className={styles.menuContainer}>
            {itemList.map((item) => {
                return (
                    <div className={styles.menuExpandedItemContainer}>
                        {item.subMenuItemList ? (
                            <MenuExpandableItem
                                iconComp ={item.iconComp}
                                iconName ={item.iconName}
                                label = {item.label}                                
                                subMenuItemList={item.subMenuItemList}
                                selectedRouteKey ={props.selectedRouteKey}
                                onClick = {(routeKey?: string) => {
                                    if (item.onClick) item.onClick(routeKey)
                                }}
                            />
                        ) : (
                            <MenuItem
                                iconComp={item.iconComp}
                                iconName={item.iconName}
                                label={item.label}
                                isFlat={props.isFlat}
                                isSelected={
                                    item.routeKey === props.selectedRouteKey
                                }
                                onClick={(routeKey?: string) => {
                                    if (item.onClick) item.onClick(routeKey)
                                }}
                            />
                        )}
                    </div>
                )
            })}
        </div>
    )
}
